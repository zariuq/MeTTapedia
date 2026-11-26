import Mettapedia.Machines.TIsa.StoreInstructions.OptionalBinding

/-!
# Executing a whole open match plan on projected candidate words

Each constructor test reads the candidate's constructor key. Each
variable test reads its presence and value, checks or writes one slot,
and continues only on success. On refusal the private binding bank
need not be cleared, because it was never published.

The source layout is a read-only path projection of one candidate.
Building that projection and publishing the accepted next match
level are separate from executing the plan.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPlan

open _root_.X86Registers X86RegisterRefinement X86Execution
open X86PlacedInstruction (At)
open X86PlacedMemory (Cell Controls Reads CodeApart footprint)
open NativeBinding (View occupancy)
open MemoryBinding (Native Known registerWrites)
open MatchPlan (Path Observation Test Field demand)
open OptionalBinding (markerLayout)
open Mettapedia.Logic.LP
local instance : MemoryPrimitives := X86Memory.ordinary

structure CellsAt (F : Type*) (pointer : Word) where
  offset : F → BitVec 32
  cell : ∀ field, Cell pointer (offset field)

def CellsAt.addr {F : Type*} {pointer : Word} (region : CellsAt F pointer) (field : F) : BitVec 48 :=
  (region.cell field).address

structure Candidate (pointer : Word) where
  tags : CellsAt Path pointer
  present : CellsAt Path pointer
  terms : CellsAt Path pointer

def Candidate.addr {pointer : Word} (input : Candidate pointer) : Field → BitVec 48
  | .tag path => input.tags.addr path
  | .present path => input.present.addr path
  | .value path => input.terms.addr path

universe u q
variable {σ : LPSignature.{u, u, q, u}} [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  {slot candidate : Word}

structure Bank (σ : LPSignature) (pointer : Word) where
  names : Finset σ.vars
  bits : CellsAt σ.vars pointer
  terms : CellsAt σ.vars pointer
  separated : ∀ v, Disjoint (footprint (terms.addr v)) (footprint (bits.addr v))

def Bank.slotWrites (bank : Bank σ slot) (name : σ.vars) : Finset ℕ :=
  footprint (bank.terms.addr name) ∪ footprint (bank.bits.addr name)

def Bank.writes (bank : Bank σ slot) : Finset ℕ := bank.names.biUnion bank.slotWrites

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem Bank.slot_subset (bank : Bank σ slot) {name : σ.vars} (member : name ∈ bank.names) :
    bank.slotWrites name ⊆ bank.writes := by
  intro byte included
  exact Finset.mem_biUnion.mpr ⟨name, member, included⟩

def Bank.cells (bank : Bank σ slot) (name : σ.vars) (start occupied success refused : ℕ) :
    X86PlacedPairStore.Cells
      (MemoryBinding.gate start occupied success refused (bank.terms.offset name) (bank.bits.offset name)).writes slot :=
  ⟨bank.terms.cell name, bank.bits.cell name, bank.separated name⟩

structure Readouts (needed : Finset Field) (tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (values : PackedOccurrences.Codes (GroundTerm σ)) (input : Candidate candidate)
    (read : Observation σ) (state : Native) : Prop where
  key : ∀ path, .tag path ∈ needed → ∃ word, tags.encode ((read path).map MatchPlan.symbol) = some word ∧
    Reads state (input.tags.addr path) word
  present : ∀ path, .present path ∈ needed → Reads state (input.present.addr path) (occupancy (read path))
  term : ∀ path, .value path ∈ needed → ∀ value, read path = some value → ∃ word, values.encode value = some word ∧
    Reads state (input.terms.addr path) word

def Bank.Represents (values : PackedOccurrences.Codes (GroundTerm σ)) (bank : Bank σ slot)
    (table : BindingSlots.Table σ) (state : Native) : Prop :=
  ∀ name ∈ bank.names, ∃ word, View values state (bank.bits.addr name) (bank.terms.addr name) (table name) word

structure Geometry (needed : Finset Field) (input : Candidate candidate) (bank : Bank σ slot)
    (image : NativeImage.View) (base : BitVec 48) : Prop where
  sourceSafe : ∀ field ∈ needed, Disjoint (footprint (input.addr field)) bank.writes
  independent : ∀ v ∈ bank.names, ∀ w ∈ bank.names, v ≠ w → Disjoint (bank.slotWrites v) (bank.slotWrites w)
  codeSafe : CodeApart image base bank.writes

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem view_preserved (codes : PackedOccurrences.Codes (GroundTerm σ))
    {before after : Native} {bits terms : BitVec 48} {binding : Option (GroundTerm σ)} {word : Word}
    {registers : Finset Register} {writes : Finset ℕ} (view : View codes before bits terms binding word)
    (frame : X86StateFrame.Frame registers writes before after)
    (bitSafe : Disjoint (footprint bits) writes) (termSafe : Disjoint (footprint terms) writes) :
    View codes after bits terms binding word :=
  ⟨view.bit.preserved frame bitSafe, view.value.preserved frame termSafe, view.code⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
private theorem readouts_preserved
    {needed : Finset Field}
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    {values : PackedOccurrences.Codes (GroundTerm σ)} {input : Candidate candidate} {bank : Bank σ slot}
    {image : NativeImage.View} {base : BitVec 48} (geometry : Geometry needed input bank image base)
    {read : Observation σ} {before after : Native} {writes : Finset ℕ} {registers : Finset Register}
    (frame : X86StateFrame.Frame registers writes before after) (within : writes ⊆ bank.writes)
    (view : Readouts needed tags values input read before) : Readouts needed tags values input read after := by
  refine ⟨?_, fun p listed => (view.present p listed).preserved frame ((geometry.sourceSafe (.present p) listed).mono_right within), ?_⟩
  · intro p listed
    obtain ⟨word, code, ready⟩ := view.key p listed
    exact ⟨word, code, ready.preserved frame ((geometry.sourceSafe (.tag p) listed).mono_right within)⟩
  · intro p listed term provided
    obtain ⟨word, code, ready⟩ := view.term p listed term provided
    exact ⟨word, code, ready.preserved frame ((geometry.sourceSafe (.value p) listed).mono_right within)⟩

private theorem known_preserved {before after : Native} {writes : Finset ℕ} (known : Known before slot candidate)
    (frame : X86StateFrame.Frame registerWrites writes before after) : Known after slot candidate :=
  ⟨(frame.lookup 6 (by decide)).trans known.slot, (frame.lookup 7 (by decide)).trans known.candidate,
    (frame.lookup 8 (by decide)).trans known.zero, (frame.lookup 9 (by decide)).trans known.one⟩

structure Ready (needed : Finset Field) (tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (values : PackedOccurrences.Codes (GroundTerm σ)) (input : Candidate candidate) (bank : Bank σ slot)
    (read : Observation σ) (table : BindingSlots.Table σ) (state : Native) : Prop where
  operands : Known state slot candidate
  projected : Readouts needed tags values input read state
  bindings : bank.Represents values table state

private theorem bank_after (values : PackedOccurrences.Codes (GroundTerm σ))
    {needed : Finset Field} {input : Candidate candidate} {bank : Bank σ slot} {image : NativeImage.View} {base : BitVec 48}
    (geometry : Geometry needed input bank image base) {before after : Native} {writes : Finset ℕ}
    (frame : X86StateFrame.Frame registerWrites writes before after) {name : σ.vars} (named : name ∈ bank.names)
    (within : writes ⊆ bank.slotWrites name) {table following : BindingSlots.Table σ} (term : GroundTerm σ)
    (matched : BindingSlots.bind table name term = some following)
    (view : bank.Represents values table before) (written : ∃ word,
      View values after (bank.bits.addr name) (bank.terms.addr name) (following name) word) :
    bank.Represents values following after := by
  intro v member
  by_cases same : v = name
  · subst v; exact written
  · have apart := (geometry.independent v member name named same).mono_right within
    obtain ⟨word, resting⟩ := view v member
    rw [BindingSlots.bind_keeps_other term same matched]
    exact ⟨word, view_preserved values resting frame (apart.mono_left Finset.subset_union_right)
      (apart.mono_left Finset.subset_union_left)⟩

inductive Site (tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (input : Candidate candidate) (bank : Bank σ slot) (image : NativeImage.View) (refused : ℕ) :
    ℕ → ℕ → Test σ → Prop where
  | shape (start : ℕ) (p : Path) (symbol : MatchPlan.Symbol σ) (expected : Word)
      (encoded : tags.encode (some symbol) = some expected)
      (placed : MemoryCompare.Checked markerLayout image start refused .equal
        (.copy (input.tags.offset p) (input.tags.cell p)) (.literal expected : NativeWords.Source slot)) :
      Site tags input bank image refused start (start + 26) (.shape p symbol)
  | bind (start occupied success : ℕ) (p : Path) (name : σ.vars) (named : name ∈ bank.names)
      (placed : OptionalBinding.Checked image start occupied success refused (bank.terms.offset name)
        (bank.bits.offset name) (input.terms.offset p) (slot := slot) (input.present.offset p) (input.present.cell p)) :
      Site tags input bank image refused start success (.bind p name)

set_option maxHeartbeats 1200000 in
theorem fetch_one (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {needed : Finset Field}
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    {values : PackedOccurrences.Codes (GroundTerm σ)} {input : Candidate candidate} {bank : Bank σ slot}
    {image : NativeImage.View} {base : BitVec 48} {start success refused : ℕ}
    {test : Test σ} (placed : Site tags input bank image refused start success test)
    {before : Native} (point : At image before base start) (controls : Controls before)
    {read : Observation σ} {table : BindingSlots.Table σ} (ready : Ready needed tags values input bank read table before)
    (observedFields : ∀ field ∈ test.fields, field ∈ needed)
    (geometry : Geometry needed input bank image base) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame registerWrites bank.writes before after ∧
      match MatchPlan.run read [test] table with
      | none => Nonempty (At image after base refused)
      | some following => Ready needed tags values input bank read following after ∧ Nonempty (At image after base success) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  cases placed with
  | shape path tag expected encoded site =>
    obtain ⟨word, code, observed⟩ := ready.projected.key path (observedFields _ List.mem_cons_self)
    obtain ⟨after, ran, frame, reached⟩ := MemoryCompare.constructor_test tags read path tag
      other extra vector markerLayout _ (input.tags.cell path) word expected code encoded point controls site
      ready.operands.candidate ready.operands.slot observed
    have unmodified : X86StateFrame.Frame registerWrites ∅ before after := frame.mono (by decide) (by simp)
    have extended := unmodified.mono (Finset.Subset.refl _) (Finset.empty_subset bank.writes)
    refine ⟨after, 4, ran, extended, ?_⟩
    cases passes : MatchPlan.shapePasses read path tag
    · simpa [MatchPlan.run, passes] using reached
    · simp only [MatchPlan.run, passes, if_true]
      refine ⟨⟨known_preserved ready.operands extended, readouts_preserved geometry extended (Finset.Subset.refl _) ready.projected, ?_⟩, ?_⟩
      · intro name wanted
        obtain ⟨value, holding⟩ := ready.bindings name wanted
        exact ⟨value, view_preserved values holding unmodified (by simp) (by simp)⟩
      · simpa [passes] using reached
  | bind occupied success path name named site =>
    obtain ⟨held, entered⟩ := ready.bindings name named
    obtain ⟨after, cost, words, ran, frame, within, result⟩ := OptionalBinding.reads_optional values table name
      (read path) other extra vector point controls (input.present.cell path) site ready.operands
      (bank.cells name _ occupied success refused)
      (input.terms.cell path) held entered
      (ready.projected.present path (observedFields _ List.mem_cons_self))
      (ready.projected.term path (observedFields _ (List.mem_cons_of_mem _ List.mem_cons_self)))
      (geometry.codeSafe.mono (bank.slot_subset named))
    have bounded : words ⊆ bank.writes := within.trans (bank.slot_subset named)
    refine ⟨after, cost, ran, frame.mono (Finset.Subset.refl _) bounded, ?_⟩
    cases observed : read path with
    | none =>
      simp only [observed, Option.bind_none] at result
      simpa [MatchPlan.run, observed] using result.2.2
    | some term =>
      simp only [observed, Option.bind_some] at result
      cases matched : BindingSlots.bind table name term with
      | none =>
        rw [matched] at result
        simpa [MatchPlan.run, observed, matched] using result.2.2
      | some following =>
        rw [matched] at result
        obtain ⟨stored, newSlot, reached⟩ := result
        simp only [MatchPlan.run, observed, matched, bind, Option.bind_some]
        exact ⟨⟨known_preserved ready.operands frame, readouts_preserved geometry frame bounded ready.projected,
          bank_after values geometry frame named within term matched ready.bindings ⟨stored, newSlot⟩⟩, reached⟩

inductive PlacedPlan (tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ)))
    (input : Candidate candidate) (bank : Bank σ slot) (image : NativeImage.View) (refused : ℕ) :
    ℕ → ℕ → List (Test σ) → Prop where
  | nil (offset : ℕ) : PlacedPlan tags input bank image refused offset offset []
  | cons {start middle success : ℕ} {test : Test σ} {rest : List (Test σ)}
      (head : Site tags input bank image refused start middle test)
      (tail : PlacedPlan tags input bank image refused middle success rest) :
      PlacedPlan tags input bank image refused start success (test :: rest)

/-- Arbitrary placed test sequences realize the pure plan with a
common refusal exit. A successful endpoint represents the entire
following binding table, not just the last slot written. -/
theorem fetch_plan (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {needed : Finset Field}
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    {values : PackedOccurrences.Codes (GroundTerm σ)} {input : Candidate candidate} {bank : Bank σ slot}
    {image : NativeImage.View} {base : BitVec 48} {start success refused : ℕ}
    {tests : List (Test σ)} (placed : PlacedPlan tags input bank image refused start success tests)
    {before : Native} (point : At image before base start) (controls : Controls before)
    {read : Observation σ} {table : BindingSlots.Table σ} (ready : Ready needed tags values input bank read table before)
    (observedFields : ∀ test ∈ tests, ∀ field ∈ test.fields, field ∈ needed)
    (geometry : Geometry needed input bank image base) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame registerWrites bank.writes before after ∧
      match MatchPlan.run read tests table with
      | none => Nonempty (At image after base refused)
      | some following => Ready needed tags values input bank read following after ∧ Nonempty (At image after base success) := by
  let : OtherOpcodeHandlers := MemoryBinding.handlers other extra
  let : VectorOpcodeHandlers := vector
  induction placed generalizing before table with
  | nil offset =>
    exact ⟨before, 0, X86FuelPrefix.fetches_zero before, X86StateFrame.Frame.refl _ _ _, ready, ⟨point⟩⟩
  | cons site tail ih =>
    obtain ⟨first, headCost, ran, framed, outcome⟩ :=
      fetch_one other extra vector site point controls ready (observedFields _ List.mem_cons_self) geometry
    rw [MatchPlan.run_cons]
    split at outcome
    next finished =>
      rw [finished]
      exact ⟨first, headCost, ran, framed, outcome⟩
    next nextTable finished =>
      rw [finished, Option.bind_some]
      obtain ⟨nextReady, ⟨nextPoint⟩⟩ := outcome
      obtain ⟨after, tailCost, later, finalFrame, done⟩ :=
        ih nextPoint (controls.transport framed (by decide)) nextReady
          (fun test listed => observedFields test (List.mem_cons_of_mem _ listed))
      exact ⟨after, headCost + tailCost, X86FuelPrefix.fetches_then _ _ before first after ran later,
        (framed.trans finalFrame).mono (by simp) (by simp), done⟩

open Derivation.FirstOrderTerms (Bindings extend)

/-- The native branches for a compiled open pattern agree with the
first-order list matcher on both refusal and every returned binding. -/
theorem fetch_pattern (other : OtherOpcodeHandlers) (extra : OtherTwoByteHandlers) (vector : VectorOpcodeHandlers)
    {tags : PackedOccurrences.Codes (Option (MatchPlan.Symbol σ))}
    {values : PackedOccurrences.Codes (GroundTerm σ)} {input : Candidate candidate} {bank : Bank σ slot}
    {image : NativeImage.View} {base : BitVec 48} {start success refused : ℕ} {pattern : Term σ}
    (placed : PlacedPlan tags input bank image refused start success (MatchPlan.compile pattern))
    {before : Native} (point : At image before base start) (controls : Controls before)
    (term : GroundTerm σ) {table : BindingSlots.Table σ} {history : Bindings σ}
    (ready : Ready (demand (MatchPlan.compile pattern)) tags values input bank (MatchPlan.observe term) table before)
    (represented : BindingSlots.Represents table history)
    (geometry : Geometry (demand (MatchPlan.compile pattern)) input bank image base) :
    letI : OtherOpcodeHandlers := MemoryBinding.handlers other extra
    letI : VectorOpcodeHandlers := vector
    ∃ after steps, (X86FuelPrefix.fetches steps).run before = .ok () after ∧
      X86StateFrame.Frame registerWrites bank.writes before after ∧
      match extend history pattern term with
      | none => Nonempty (At image after base refused)
      | some binding => ∃ following, bank.Represents values following after ∧
          BindingSlots.Represents following binding ∧ Nonempty (At image after base success) := by
  obtain ⟨after, steps, fetched, frame, outcome⟩ :=
    fetch_plan other extra vector placed point controls ready (fun _ listed _ used => MatchPlan.demand_covers listed used) geometry
  refine ⟨after, steps, fetched, frame, ?_⟩
  have accepts := MatchPlan.run_accepts.{0, u, q} represented pattern term
  cases decision : MatchPlan.run (MatchPlan.observe term) (MatchPlan.compile pattern) table with
  | none =>
    rw [decision] at outcome accepts
    cases reference : extend history pattern term with
    | none => exact outcome
    | some _ => rw [reference] at accepts; cases accepts
  | some following =>
    rw [decision] at outcome accepts
    cases reference : extend history pattern term with
    | none => rw [reference] at accepts; cases accepts
    | some binding =>
      exact ⟨following, outcome.1.bindings,
        MatchPlan.run_represents.{0, u, q} represented pattern term decision reference, outcome.2⟩

end Mettapedia.Machines.TIsa.StoreInstructions.NativeMatchPlan
