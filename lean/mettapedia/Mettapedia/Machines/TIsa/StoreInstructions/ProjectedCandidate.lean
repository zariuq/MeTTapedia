import Mettapedia.Machines.TIsa.StoreInstructions.CandidateProjection
import Mettapedia.Machines.TIsa.StoreInstructions.WordRegion

/-!
# Native placement of a candidate projection

The pattern determines the offsets in every candidate bank. A proof
of a word read recovers exactly the corresponding observation. For a
field outside the demand the total address map may use a default
cell, which no instruction in the compiled plan reads.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.ProjectedCandidate

open Mettapedia.Logic.LP
open MatchPlan (Test Field Path demand)
open CandidateProjection (fields column column_bound column_inj wordFor project)
open PackedOccurrences (Codes)
open X86PlacedMemory (Reads footprint)
open NativeMatchPlan (Candidate CellsAt Readouts)

universe u q
variable {σ : LPSignature.{u,u,q,u}}

def capacity (tests : List (Test σ)) : ℕ := max 1 (fields tests).length

def nativeColumn (tests : List (Test σ)) (field : Field) : Fin (capacity tests) :=
  if fits : column tests field < (fields tests).length then
    ⟨column tests field, fits.trans_le (Nat.le_max_right _ _)⟩
  else ⟨0, lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)⟩

theorem nativeColumn_val {tests : List (Test σ)} {field : Field} (needed : field ∈ demand tests) :
    (nativeColumn tests field).val = column tests field := by
  rw [nativeColumn, dif_pos (column_bound needed)]

abbrev Region (tests : List (Test σ)) := WordRegion.Region (capacity tests)

def cells (tests : List (Test σ)) (region : Region tests) (kind : Path → Field) : CellsAt Path region.pointer :=
  ⟨fun p => BitVec.ofNat 32 (WordRegion.offset (nativeColumn tests (kind p))),
    fun p => region.cell (nativeColumn tests (kind p))⟩

def candidate (tests : List (Test σ)) (region : Region tests) : Candidate region.pointer :=
  ⟨cells tests region .tag, cells tests region .present, cells tests region .value⟩

theorem address (tests : List (Test σ)) (region : Region tests) (field : Field) :
    (candidate tests region).addr field = (region.cell (nativeColumn tests field)).address := by
  cases field <;> rfl

theorem separate_fields {tests : List (Test σ)} (region : Region tests) {left right : Field}
    (l : left ∈ demand tests) (r : right ∈ demand tests) (different : left ≠ right) :
    Disjoint (footprint ((candidate tests region).addr left)) (footprint ((candidate tests region).addr right)) := by
  rw [address, address]
  apply region.separate_words
  intro same
  have equal := congrArg Fin.val same
  rw [nativeColumn_val l, nativeColumn_val r] at equal
  exact different (column_inj l r equal)

def Memory {tests : List (Test σ)} (region : Region tests) (words : Array Word) (state : MemoryBinding.Native) : Prop :=
  ∀ (i : Fin (capacity tests)) (value : Word), words[i.val]? = some value →
    Reads state (region.cell i).address value

theorem Memory.preserved {tests : List (Test σ)} {region : Region tests} {words : Array Word}
    {before after : MemoryBinding.Native} {regs : Finset _root_.X86Registers.Register}
    (resident : Memory region words before) (frame : X86StateFrame.Frame regs ∅ before after) :
    Memory region words after :=
  fun i value stored => (resident i value stored).preserved frame (by simp)

theorem readouts (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    {tests : List (Test σ)} (region : Region tests) {term : GroundTerm σ} {words : Array Word}
    (formed : project tags values tests term = some words)
    {state : MemoryBinding.Native} (loaded : Memory region words state) :
    Readouts (demand tests) tags values (candidate tests region) (MatchPlan.observe term) state := by
  obtain ⟨width, expected⟩ := CandidateProjection.project_shape tags values formed
  have read_field (field : Field) (needed : field ∈ demand tests) :
      ∃ word, wordFor tags values (MatchPlan.observe term) field = some word ∧
        Reads state ((candidate tests region).addr field) word := by
    have within : column tests field < words.size := width.symm ▸ column_bound needed
    have reads := Array.getElem?_eq_getElem within
    have real := loaded (nativeColumn tests field) (getElem words (column tests field) within)
      (by rw [nativeColumn_val needed]; exact reads)
    exact ⟨_, (expected field needed).symm.trans reads, (address tests region field).symm ▸ real⟩
  refine ⟨?_, ?_, ?_⟩
  · intro path needed
    exact read_field (.tag path) needed
  · intro path needed
    obtain ⟨word, encoded, ready⟩ := read_field (.present path) needed
    exact (Option.some.inj encoded).symm ▸ ready
  · intro path needed term observed
    obtain ⟨word, code, ready⟩ := read_field (.value path) needed
    exact ⟨word, by simpa only [wordFor, observed] using code, ready⟩

/-- The array of candidate banks is in lockstep with the projection
array; its ordinal, not the value of a term, selects a bank. -/
def Banks (tests : List (Test σ)) (directory : Array (Array Word))
    (regions : Array (Region tests)) (state : MemoryBinding.Native) : Prop :=
  ∀ (index : ℕ) (words : Array Word), directory[index]? = some words →
    ∃ region : Region tests, regions[index]? = some region ∧ Memory region words state

theorem Banks.preserved {tests : List (Test σ)} {directory : Array (Array Word)}
    {regions : Array (Region tests)} {before after : MemoryBinding.Native} {regs : Finset _root_.X86Registers.Register}
    (resident : Banks tests directory regions before) (frame : X86StateFrame.Frame regs ∅ before after) :
    Banks tests directory regions after := by
  intro index words selected
  obtain ⟨region, allocated, loaded⟩ := resident index words selected
  exact ⟨region, allocated, loaded.preserved frame⟩

theorem selected (tags : Codes (Option (MatchPlan.Symbol σ))) (values : Codes (GroundTerm σ))
    (tests : List (Test σ)) {store : Derivation.Store (GroundTerm σ)}
    {packed : PackedOccurrences.Layout} {directory : Array (Array Word)} {regions : Array (Region tests)}
    {state : MemoryBinding.Native} (formed : PackedOccurrences.pack values store = some packed)
    (projected : CandidateProjection.prepare tags values tests packed = some directory)
    (resident : Banks tests directory regions state) {index identity : ℕ} {term : GroundTerm σ}
    (occurrence : PackedOccurrences.at? values packed index = some (identity, term)) :
    ∃ region, regions[index]? = some region ∧
      Readouts (demand tests) tags values (candidate tests region) (MatchPlan.observe term) state := by
  obtain ⟨words, row, expect⟩ := CandidateProjection.selected_projection tags values tests
    formed projected index identity term occurrence
  obtain ⟨region, allocated, loaded⟩ := resident index words row
  exact ⟨region, allocated, readouts tags values region expect loaded⟩

variable {tests : List (Test σ)} {slot : Word}

/-- Moving from one candidate bank to another requires no code patch.
Each cell proof changes, but the pattern's displacements do not. -/
theorem relocate {tags : Codes (Option (MatchPlan.Symbol σ))} {bank : NativeMatchPlan.Bank σ slot}
    {image : NativeImage.View} {refused start success : ℕ} {plan : List (Test σ)}
    (old next : Region tests)
    (placed : NativeMatchPlan.PlacedPlan tags (candidate tests old) bank image refused start success plan) :
    NativeMatchPlan.PlacedPlan tags (candidate tests next) bank image refused start success plan := by
  induction placed with
  | nil offset => exact .nil offset
  | cons current _ later =>
    apply NativeMatchPlan.PlacedPlan.cons _ later
    cases current with
    | shape p tag expected encoded checked =>
      exact .shape _ p tag expected encoded ⟨checked.prefixFits, checked.loadLeft, checked.loadRight, checked.compare⟩
    | bind occupied _ p name named checked =>
      exact .bind _ occupied _ p name named
        ⟨⟨checked.mark.prefixFits, checked.mark.loadLeft, checked.mark.loadRight, checked.mark.compare⟩, checked.bind⟩

end Mettapedia.Machines.TIsa.StoreInstructions.ProjectedCandidate
